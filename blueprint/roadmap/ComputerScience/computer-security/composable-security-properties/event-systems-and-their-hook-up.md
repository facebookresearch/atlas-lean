# Event systems and their hook-up

For a sequence $\alpha$ of events and a set $E'$ of events, the *restriction* $\alpha \upharpoonright E'$ deletes from $\alpha$ the events not in $E'$. An *event system*
$ES = (E, I, O, T)$ consists of a set $E$ of events, disjoint sets $I, O \subseteq E$ of *input* and *output* events, and a set $T \subseteq E^*$ of finite *traces*. $T$ is
*input total* if $\alpha \in T$ and $x \in I$ imply $\alpha^\frown\langle x\rangle \in T$, and *event-separable* if it is closed under initial segments; event systems are assumed to have both
properties. $ES$ is a *simple hook-up* of $ES_1 = (E_1, I_1, O_1, T_1)$ and $ES_2 = (E_2, I_2, O_2, T_2)$ if

$$E = E_1 \cup E_2, \quad I = (I_1 - O_2) \cup (I_2 - O_1), \quad O = (O_1 - I_2) \cup (O_2 - I_1),$$

$I_1 \cap I_2 = O_1 \cap O_2 = \emptyset$, the internal events of each component, $E_i - I_i - O_i$, are disjoint from the other component's events, and
$T = \{\alpha \in E^* \mid \alpha \upharpoonright E_1 \in T_1,\ \alpha \upharpoonright E_2 \in T_2\}$. Outputs of one component that are inputs of the other become internal events of the
composite.

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Sections 9.1–9.3 and 9.6 (Definitions 1–3, 7 and 8).
