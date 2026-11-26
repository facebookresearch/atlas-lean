# Hypotheses on a Duhamel operator

For $\tau \in \mathbb{R}$, a map $\Psi$ assigning to integrators $A, B : \mathbb{R} \to \mathbb{R}$ a continuous linear operator $\Psi_{A,B}$ on the bounded functions on $[0, \tau]$ (sup norm) satisfies the Duhamel-operator hypotheses when, for all $A, B$ of bounded variation on $[0, \tau]$:

- whenever the two-tag sums of $u \mapsto \prod_{(0,u]}(1 + dA)$ and $x \mapsto \prod_{(x,t]}(1 + dB)$ against $h$ (extended by $0$ outside $[0, \tau]$) over the partitions of $[0, t]$ converge along refinement to $I$, $\Psi_{A,B}\, h\, (t) = I$;
- $\|\Psi_{A,B}\| \le 6\, e^{V(A)}\, e^{V(B)}$, with $V(\cdot)$ the total variation on $[0, \tau]$;
- for $d$ with $d(t) = B(t) - A(t)$ on $[0, \tau]$, $\Psi_{A,B}\, d\, (t) = \prod_{(0,t]}(1 + dB) - \prod_{(0,t]}(1 + dA)$.
