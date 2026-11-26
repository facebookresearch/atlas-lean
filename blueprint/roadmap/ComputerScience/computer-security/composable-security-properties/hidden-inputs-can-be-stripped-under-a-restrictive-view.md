# Hidden inputs can be stripped under a restrictive view

**Theorem.** Let $v$ be a [restrictive view](restrictive-views.md) of an event system $(E, I, O, T)$ and $\alpha^\frown\gamma_1 \in T$. Then there is $\gamma_2 \in E^*$ with
$\alpha^\frown\gamma_2 \in T$, $\gamma_2 \upharpoonright v = \gamma_1 \upharpoonright v$ and $\gamma_2 \upharpoonright (I - v) = \langle\rangle$: all inputs hidden from $v$ after any point can be removed without
changing what $v$ sees.

The proof is by induction on the number of hidden inputs in $\gamma_1$, removing the last block of them with restrictiveness.

## Depends on

- [Restrictive views](restrictive-views.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Section 9.6.2, Theorem 1 and its proof.
