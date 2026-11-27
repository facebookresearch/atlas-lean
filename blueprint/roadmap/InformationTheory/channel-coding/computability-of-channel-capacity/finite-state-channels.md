# Finite-state channels and their capacity

A finite-state channel is a discrete channel with memory: a hidden state, taking finitely many values, determines together with the current input both the distribution of the output and the next state. Its capacity is the supremum of the rates at which messages can be sent with vanishing error.

**Definition.** Fix finite input, output and state alphabets $\mathcal{X}$, $\mathcal{Y}$, $\mathcal{S}$. A *finite-state channel* (FSC, also finite-state machine channel) is given by conditional probabilities $p(y, s \mid x, s')$, the probability of output $y$ and next state $s$ when the input is $x$ and the current state is $s'$, together with an initial state $s_0 \in \mathcal{S}$. It is in *product form* if

$$
p(y, s \mid x, s') = p(y \mid x, s')\, q(s \mid x, s').
$$

Over $n$ uses the channel acts by

$$
p^n(y^n, s_n \mid x^n, s_0) = \sum_{s_{n-1} \in \mathcal{S}} p(y_n, s_n \mid x_n, s_{n-1})\, p^{n-1}(y^{n-1}, s_{n-1} \mid x^{n-1}, s_0), \qquad p^n(y^n \mid x^n, s_0) = \sum_{s_n} p^n(y^n, s_n \mid x^n, s_0).
$$

An $(n, M)$-*code* consists of an encoder sending a message $m \in \{1, \dots, M\}$ (and the initial state) to a codeword in $\mathcal{X}^n$ and a decoder sending an output word (and the initial state) to a message; its average error probability is computed with $p^n(\cdot \mid \cdot, s_0)$. A rate $R > 0$ is *achievable* if for every $\tau > 0$ there are $(n, M)$-codes for all large $n$ with $\frac{1}{n} \log M > R - \tau$ and average error probability tending to $0$. The *capacity* $C$ of the channel is the supremum of the achievable rates; it depends on $p$, $q$ and $s_0$.

The capacity is given in general by the Verdú–Han formula, the supremum over input processes of the inf-information rate. For *information stable* channels it is the limit of the normalized mutual information rate, and for *indecomposable* channels, in which the effect of the initial state vanishes, it equals the common limit of $\frac{1}{n} \max_{X^n} \min_{s_0} I(X^n; Y^n \mid s_0)$ and $\frac{1}{n} \max_{X^n} \max_{s_0} I(X^n; Y^n \mid s_0)$ (Gallager).

## Depends on

- [Conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Proof depends on

None.

## Expansion

This page states definitions.

## Sources

- H. Boche, R. F. Schaefer and H. V. Poor, "Shannon meets Turing: non-computability and non-approximability of the finite state channel capacity", Communications in Information and Systems 20 (2020), no. 2, 81–116, https://doi.org/10.4310/CIS.2020.v20.n2.a1; read in arXiv:2008.13270v2 (Section 3, the definitions of codes, achievable rates, capacity and indecomposable channels, of arXiv:2008.13270v2).
- D. Elkouss and D. Pérez-García, "Memory effects can make the transmission capability of a communication channel uncomputable", Nature Communications 9 (2018), article 1149, https://doi.org/10.1038/s41467-018-03428-0; read in arXiv:1601.06101v3 (the section "Notation and main statements" of arXiv:1601.06101v3).
