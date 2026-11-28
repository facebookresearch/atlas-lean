# Löb induction

Löb induction lets a proof assume its own goal one step later: in the step-indexed model of Iris, $\triangleright P \Rightarrow P$ entails $P$, by induction on the step index.

**Theorem.** For every proposition $P$ of $\mathrm{UPred}(M)$, $M$ a unital camera, with $\triangleright$ and $\Rightarrow$ interpreted as in the Iris base logic, $(\triangleright P \Rightarrow P) \models P$.

## Depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)

## Proof depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)

## Expansion

Fix $a$ and show by induction on $n$ that $n \in \mathcal{V}(a)$ and $n \in (\triangleright P \Rightarrow P)(a)$ give $n \in P(a)$. At $n = 0$, $\triangleright P$ holds and $a \preccurlyeq a$ (unitality), so the implication gives $0 \in P(a)$. At $n + 1$, the implication restricts to index $n$ and validity is downward closed, so $n \in P(a)$ by induction, hence $n + 1 \in (\triangleright P)(a)$ and the implication gives $n + 1 \in P(a)$.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.5, Section 5.6 (Löb induction proved by induction on the step index), Figure 10 and Figure 11 (rule LÖB).
