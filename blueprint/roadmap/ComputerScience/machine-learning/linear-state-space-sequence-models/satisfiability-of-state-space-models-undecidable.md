# Satisfiability of state space models is undecidable

A state space model reads a word through layers of linear recurrences followed by small ReLU networks and accepts it when its final output is $1$. Whether some input word is accepted is undecidable, already for three-layer models that are both time-invariant and diagonal, and still with precision growing logarithmically in the input length.

**Setting (Alsmann and Lange).** An *SSM layer* $(h_0, \mathit{gate}, \mathit{inc}, \phi)$ of dimension $d$ has an initial vector $h_0 \in \mathbb{R}^d$ and maps $\mathit{gate} : \mathbb{R}^d \to \mathbb{R}^{d \times d}$, $\mathit{inc} : \mathbb{R}^d \to \mathbb{R}^d$ and $\phi : \mathbb{R}^d \times \mathbb{R}^d \to \mathbb{R}^d$, with $\phi$ computed by a feedforward ReLU network; it maps a sequence $x_1 \cdots x_k$ of vectors to $z_1 \cdots z_k$ through

$$
h_t = \mathit{gate}(x_t)\, h_{t-1} + \mathit{inc}(x_t), \qquad z_t = \phi(h_t, x_t) \qquad (1 \le t \le k).
$$

An *SSM* $\mathcal{S} = (\mathit{emb}, l_1, \dots, l_L, \mathit{out})$ over a finite alphabet $\Sigma$ embeds a word $w = a_1 \cdots a_k$ letterwise by $\mathit{emb} : \Sigma \to \mathbb{R}^d$, applies the layers $l_1, \dots, l_L$ in turn, and outputs $\mathcal{S}(w) = \mathit{out}(z^L_k)$, where $\mathit{out}$ is a feedforward ReLU network applied to the last vector of the last layer; $\mathcal{S}$ *accepts* $w$ if $\mathcal{S}(w) = 1$. All weights have finite representations. The SSM is *time-invariant* if every gate is constant, $\mathit{gate}(x) = A$, and *diagonal* if every $\mathit{gate}(x)$ is a diagonal matrix. For a class $\mathcal{C}$ of SSMs, $\mathrm{ssmSAT}[\mathcal{C}]$ asks, given $\mathcal{S} \in \mathcal{C}$, whether $\mathcal{S}$ accepts some word; in $\mathrm{ssmSAT}^{\mathrm{fix}}_{\log}[\mathcal{C}]$ the model is evaluated on $w$ in fixed-width arithmetic with $O(\log \max(|\Sigma|, |w|))$ bits.

**Theorem (Alsmann and Lange).** For the class of SSMs that are both time-invariant and diagonal, $\mathrm{ssmSAT}$ and $\mathrm{ssmSAT}^{\mathrm{fix}}_{\log}$ are undecidable.

The same paper shows that bounding the context length or the bit-width makes the problem decidable: with a unary bound on the word length it is NP-complete, and with a constant bit-width it lies in PSPACE, being PSPACE-complete for diagonal SSMs.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

From a Minsky machine $M$ the proof builds a three-layer SSM of dimension $2|Q| + 9$ that accepts exactly the words of state-action pairs encoding accepting runs of $M$ from $(q_0, 0, 0)$. The first layer accumulates the counter values by an identity recurrence on two coordinates. The second recovers the previous state through the recurrence $h_t = \tfrac{1}{4} h_{t-1} + x_t$, which stores the history in the binary expansion of a value that a ReLU network decodes, and its output network checks each transition and its counter condition. The third layer sums the check flags, and the output network accepts when no check failed and the last state is final. Since the counters grow at most linearly, logarithmic precision suffices for the same construction.

## Sources

- Eric Alsmann and Martin Lange, *The Computational Complexity of Satisfiability in State Space Models*, ECAI 2025, Frontiers in Artificial Intelligence and Applications, IOS Press, 2025, https://doi.org/10.3233/FAIA251006; the definitions of SSM layers and of the satisfiability problems, and the undecidability theorems for arbitrary and logarithmic precision, read in arXiv:2508.18162v1.
