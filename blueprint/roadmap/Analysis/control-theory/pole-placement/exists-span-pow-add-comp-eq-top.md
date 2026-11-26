# Heymann's lemma

Let $V$ be an $n$-dimensional vector space over a field, $U$ a vector space, and $A : V \to V$, $B : U \to V$ linear maps satisfying the Kalman rank condition $\operatorname{Span} \{ A^i B u : u \in U, \ 0 \le i < n \} = V$. Then there are $f \in U$ and a linear map $C : V \to U$ such that $B f, (A + BC) B f, \dots, (A + BC)^{n-1} B f$ span $V$: the single-input system $\dot x = (A + BC) x + (Bf) v$ satisfies the Kalman rank condition.

This is Heymann's lemma (Heymann 1968), as stated in Coron, *Control and Nonlinearity* (AMS 2007), Lemma 10.3, whose proof follows Hautus. The proof is Coron's: take $f$ with $Bf \ne 0$, build a longest linearly independent chain $x_1 = Bf, x_2, \dots, x_k$ with $x_{j+1} \in A x_j + B U$; maximality gives $A x_k + BU \subseteq E = \operatorname{Span}\{x_1, \dots, x_k\}$, hence $BU \subseteq E$ and $AE \subseteq E$, so $E$ contains the Kalman subspace and $k = n$; then $C x_j = u_j$, where $x_{j+1} = A x_j + B u_j$, gives $(A + BC)^{j} x_1 = x_{j+1}$.

## Background

- [Kalman rank condition](../controllability-of-linear-systems/is-controllable-on-iff-kalman.md): the hypothesis and the conclusion are Kalman rank conditions, equivalent to controllability of $(A, B)$ and of $(A + BC, Bf)$; Coron states the lemma for controllable systems and passes through this equivalence, the statement here does not need it.
