# Restrictive views

A view $v$ of an [event system](event-systems-and-their-hook-up.md) $(E, I, O, T)$ is *restrictive* if for all $\alpha \in T$, all $\beta_1, \beta_2 \in I^*$ and all $\gamma_1 \in E^*$ with

$$\alpha^\frown\beta_1^\frown\gamma_1 \in T, \qquad \beta_1 \upharpoonright v = \beta_2 \upharpoonright v, \qquad \gamma_1 \upharpoonright (I - v) = \langle\rangle,$$

there is $\gamma_2 \in E^*$ with

$$\alpha^\frown\beta_2^\frown\gamma_2 \in T, \qquad \gamma_2 \upharpoonright v = \gamma_1 \upharpoonright v, \qquad \gamma_2 \upharpoonright (I - v) = \langle\rangle.$$

Changing inputs hidden from $v$ in the last block of inputs can be compensated by changing later events hidden from $v$, with no new hidden input.

## Depends on

- [Event systems and their hook-up](event-systems-and-their-hook-up.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Section 9.6.1, Definition 12 (restrictiveness).
