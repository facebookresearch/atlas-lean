# Monogamy-of-entanglement property of coset states

For a subspace $A\subseteq\mathbb{F}_2^{n}$ and $s,s'\in\mathbb{F}_2^{n}$ let $|A_{s,s'}\rangle=X^{s}Z^{s'}|A\rangle$ be the coset state. In the *coset-monogamy game* ($n\ge2$ even), a challenger picks a uniformly random subspace $A$ of dimension $n/2$ and uniformly random $s,s'\in\mathbb{F}_2^{n}$ and sends $|A_{s,s'}\rangle$ to an adversary $\mathcal{A}_0$, who applies a channel producing a bipartite state and sends one register to each of the non-communicating parties $\mathcal{A}_1,\mathcal{A}_2$; then both receive a basis of $A$, and they win if $\mathcal{A}_1$ outputs an element of $A+s$ and $\mathcal{A}_2$ outputs an element of $A^{\perp}+s'$. Every (unbounded) strategy wins with probability at most $\sqrt{e}\,\cos(\pi/8)^{n}$ (Culf–Vidick, Theorem 2.1; this is the strong monogamy property conjectured by Coladangelo et al.). A distinct computational statement holds in the variant in which $\mathcal{A}_0$ additionally receives $\mathsf{iO}(A+s)$ and $\mathsf{iO}(A^{\perp}+s')$, membership programs for the two cosets: assuming post-quantum indistinguishability obfuscation and one-way functions, every QPT strategy wins with negligible probability.

## Proof sketch

For the information-theoretic bound, purify the challenger's choice with EPR pairs, so that the winning probability is the expectation over $A$ of $\sum_{s,s'}\operatorname{Tr}\bigl[(|A_{s,s'}\rangle\langle A_{s,s'}|\otimes B^{A}_{s}\otimes C^{A}_{s'})\rho\bigr]$ for a fixed state $\rho$ and the parties' POVMs. Bound the operator norm of the resulting tripartite operator with the technique used for the BB84 monogamy game, using the overlap structure of cosets of different subspaces; a second proof reduces the coset game to a variant of the BB84 monogamy game. The computational version reduces to the information-theoretic one: using subspace hiding and re-randomized shifts, a sequence of hybrids replaces the two membership programs by obfuscated membership programs for $B+t$ and $C^{\perp}+t'$, where $B\supseteq A$ has dimension $3n/4$, $C\subseteq A$ has dimension $n/4$, and $t\in s+B$, $t'\in s'+C^{\perp}$ are random. Once $B,C,t,t'$ are given in the clear, winning amounts to the information-theoretic game for a coset state of the random subspace $A$ between $C$ and $B$.

## Depends on

- [Coset states](coset-states.md)
- [Indistinguishability and virtual black-box obfuscation](../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Monogamy-of-entanglement game for BB84 states](monogamy-bb84.md)

## Sources

- Eric Culf, Thomas Vidick, "A monogamy-of-entanglement game for subspace coset states", Quantum 6, 791 (2022), Theorem 2.1, arXiv:2107.13324.
- Andrea Coladangelo, Jiahui Liu, Qipeng Liu, Mark Zhandry, "Hidden Cosets and Applications to Unclonable Cryptography", CRYPTO (2021), IACR ePrint 2021/946, §4.4 (conjecture and computational version).
