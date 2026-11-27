# Binary stochastic BTSP rule and its synapse activation probabilities

**Model.** Input neurons ($m$ of them, modeling hippocampal CA3) project to $n$ memory neurons (CA1) through binary weights $w_{ji}\in\{0,1\}$, each connection present independently with probability $f_w$. Memory items are binary vectors $x\in\{0,1\}^m$ with i.i.d. entries equal to $1$ with probability $f_p$. During one-shot learning of $M$ items $x^1,\dots,x^M$, each memory neuron independently receives a plateau potential (a gating signal from entorhinal cortex) for each item with probability $f_q$, and a plateau triggers an update of the neuron with probability $1/2$, so each memory neuron is updated for each item independently with probability $f_q/2$ (the source's core BTSP rule). When neuron $j$ is updated while item $x$ is presented, each of its synapses changes by the **binary BTSP rule**

$$\Delta w_{ji} = \begin{cases} +1 & \text{if } x_i = 1 \text{ and } w_{ji} = 0,\\ -1 & \text{if } x_i = 1 \text{ and } w_{ji} = 1,\end{cases}$$

and is otherwise unchanged. The update does not depend on postsynaptic firing, and its direction depends only on the current weight: a synapse toggles. Memory neurons are McCulloch–Pitts units firing iff $u_j(x) = \sum_i w_{ji}x_i > v_{th}$; the memory trace $z(x)$ is the set of neurons firing in response to $x$ after learning.

**Parity lemma.** If $X\sim\mathrm{Bin}(N, p)$ then

$$P(X\text{ even}) = \tfrac12\big(1 + (1-2p)^N\big),\qquad P(X\text{ odd}) = \tfrac12\big(1 - (1-2p)^N\big).$$

**Synapse activation probabilities.** Starting from zero weights, $w_{ji}$ equals the parity of the number of toggles it received. Fix an item $x$ and $i\in\operatorname{supp}(x)$, and let $Q(x)$ be the neurons updated for $x$. Each of the other $M-1$ items toggles the synapse independently with probability $f_pf_q/2$, so for a present connection

$$p_e := P(w_{ji} = 1\mid j\in Q(x)) = \tfrac12\big(1 + (1 - f_pf_q)^{M-1}\big),\qquad p_o := P(w_{ji} = 1\mid j\notin Q(x)) = \tfrac12\big(1 - (1 - f_pf_q)^{M-1}\big),$$

the first counting the toggle caused by $x$ itself. Treating synapses as independent, with $F(\cdot\,; I, q)$ the binomial CDF and $I = |\operatorname{supp}(x)|$,

$$p_{f1} = 1 - F(v_{th}; I, f_wp_e),\qquad p_{f2} = 1 - F(v_{th}; I, f_wp_o),$$

and the firing probability of a memory neuron for $x$ is

$$p_f^{\mathrm{avg}} = \sum_{I=0}^m \binom{m}{I}f_p^I(1-f_p)^{m-I}\big[\tfrac{f_q}{2}\,p_{f1}(I) + \big(1-\tfrac{f_q}{2}\big)\,p_{f2}(I)\big].$$

Since $p_e > 1/2 > p_o$ for every finite $M$, neurons gated during learning of $x$ fire preferentially when $x$ is replayed; the gap $p_e - p_o = (1-f_pf_q)^{M-1}$ decays geometrically in the number of stored items, which sets the memory capacity. The source calls these quantities estimates. The certain update of every synapse of an updated neuron matters: if instead each synapse of a neuron with a plateau toggled independently with probability $1/2$, then $P(w_{ji} = 1\mid j \text{ had a plateau for } x) = 1/2$ exactly, since adding an independent fair toggle makes the parity uniform.

## Expansion

The lemma follows by adding and subtracting the binomial expansions of $((1-p)+p)^N$ and $((1-p)-p)^N$. For $j\in Q(x)$ the toggle count is $1 + \mathrm{Bin}(M-1, f_pf_q/2)$, which is odd exactly when the binomial part is even, giving $p_e$; for $j\notin Q(x)$ it is $\mathrm{Bin}(M-1, f_pf_q/2)$, giving $p_o$. A memory neuron lies in $Q(x)$ with probability $f_q/2$, which gives the weights in $p_f^{\mathrm{avg}}$. The same per-neuron firing probabilities, combined with a masked cue $x'$ having a fraction of its 1's set to 0, give the expected Hamming distance between the traces $z(x)$ and $z(x')$, which shows that binary-weight BTSP yields a content-addressable memory recalling from partial cues.

## Sources

- Y. Wu, W. Maass, *A simple model for Behavioral Time Scale Synaptic Plasticity (BTSP) provides content addressable memory with binary synapses and one-shot learning*, Nature Communications 16 (2025), 342, Results (Eq. 1) and Methods (Lemma 1, Eqs. 2–3, 8–16). <https://doi.org/10.1038/s41467-024-55563-6> (PMCID: PMC11695864)
