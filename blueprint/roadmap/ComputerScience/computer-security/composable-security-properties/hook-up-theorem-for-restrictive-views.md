# The hook-up theorem for restrictive views

**Theorem (McCullough).** Let $ES$ be the [simple hook-up](event-systems-and-their-hook-up.md) of $ES_1 = (E_1, I_1, O_1, T_1)$ and $ES_2 = (E_2, I_2, O_2, T_2)$, and let $v$ be a
view of $ES$ such that $v \cap E_1$ is a [restrictive view](restrictive-views.md) of $ES_1$ and $v \cap E_2$ is a restrictive view of $ES_2$. Then $v$ is a restrictive view of $ES$.

The proof merges component histories that agree on a common prefix and on the shared events of $v$ afterwards into a single composite history with the same
view.

## Depends on

- [Restrictive views](restrictive-views.md)

## Proof depends on

- [Hidden inputs can be stripped under a restrictive view](hidden-inputs-can-be-stripped-under-a-restrictive-view.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Section 9.7, the merging construction (Theorems 2–4) and Theorem 5 with its proof.
