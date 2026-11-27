# Consistency, best string, equivalence and minimization of RNN language models are undecidable

A single-layer recurrent neural network with ReLU activations and softmax predictions assigns a weight to every string, the product of its next-token probabilities. Whether these weights sum to $1$, whether some string has weight above a threshold, whether two networks agree, and whether fewer neurons suffice are all undecidable.

**Setting (Chen, Gilroy, Maletti, May and Knight).** Let $\Sigma$ be an alphabet and $\dashv \notin \Sigma$ an end marker (the source writes a dollar sign), $\Sigma_{\dashv} = \Sigma \cup \{\dashv\}$. A *single-layer RNN* $R = \langle \Sigma, N, h_{-1}, W, W', E, E' \rangle$ has a finite set $N$ of neurons, an initial vector $h_{-1} \in \mathbb{Q}^N$, a transition matrix $W \in \mathbb{Q}^{N \times N}$, bias vectors $W'_a \in \mathbb{Q}^N$ for $a \in \Sigma_{\dashv}$, a prediction matrix $E \in \mathbb{Q}^{\Sigma_{\dashv} \times N}$ and a prediction bias $E' \in \mathbb{Q}^{\Sigma_{\dashv}}$. On input $s = s_1 \cdots s_n$, with $s_0 = s_{n+1} = \dashv$, the hidden states are $h_{s,t} = \sigma(W h_{s,t-1} + W'_{s_t})$ for $0 \le t \le n$, where $\sigma$ is the componentwise ReLU $v \mapsto \max(0, v)$, and the next-token distribution is $\mathrm{softmax}(E h_{s,t} + E')$, where $\mathrm{softmax}(p)(a) = e^{p(a)} / \sum_{a' \in \Sigma_{\dashv}} e^{p(a')}$ (the denominator is a positive sum over all of $\Sigma_{\dashv}$). The RNN computes the weighted language

$$
R(s) = \prod_{t=0}^{n} \mathrm{softmax}(E h_{s,t} + E')(s_{t+1}).
$$

$R$ is *consistent* if $\sum_{s \in \Sigma^*} R(s) = 1$.

**Theorem (Chen, Gilroy, Maletti, May and Knight).** The following problems are undecidable:

1. *consistency*: given an RNN $R$, is $R$ consistent?
2. *best string*: given an RNN $R$ and $c \in (0, 1)$, is there $s \in \Sigma^*$ with $R(s) > c$?
3. *equivalence*: given RNNs $R$ and $R'$, is $R(s) = R'(s)$ for all $s \in \Sigma^*$?
4. *minimization*: given an RNN $R$ and $n \in \mathbb{N}$, is there an RNN with at most $n$ neurons computing the same weighted language?

Moreover, no computable function bounds the length of a highest-weighted string of a consistent RNN in terms of the size of the RNN. In contrast, the best string problem is decidable for consistent RNNs, and NP-complete when restricted to strings of polynomial length.

## Depends on

None.

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

All four reductions start from Siegelmann and Sontag's theorem that, for every deterministic Turing machine $M$, a network with saturated linear activation over a one-letter alphabet has a neuron that takes the value $1$ exactly at step $T$ if $M$ halts on empty input after $T$ steps, and stays $0$ if $M$ does not halt. Since saturated linear activation is a difference of two ReLUs, a ReLU network with two designated neurons simulates it. Feeding the difference of these neurons into the predictions of a small example network yields an RNN that is consistent, has a string of weight above $0.25$, differs from a fixed trivial network, and needs at least one neuron, each exactly when $M$ halts. A good expansion adds and links a page for the Siegelmann–Sontag simulation of Turing machines by recurrent networks.

## Sources

- Yining Chen, Sorcha Gilroy, Andreas Maletti, Jonathan May and Kevin Knight, *Recurrent Neural Networks as Weighted Language Recognizers*, Proceedings of NAACL-HLT 2018, Volume 1, Association for Computational Linguistics, 2018, pp. 2261–2271, https://doi.org/10.18653/v1/N18-1205; Definitions 1 and 2, Theorems 6, 8, 9, 10, 11, 12 and 13, read in the open-access copy at https://aclanthology.org/N18-1205.pdf and in arXiv:1711.05408v2.
