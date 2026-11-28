# Inbreeding coefficient under partial self-fertilization

Consider an infinite hermaphroditic population without selection in which, every generation, each
individual is produced by self-fertilization with probability $S \in [0, 1]$ and otherwise by random
outcrossing, the two parents of an outcrossed individual being distinct and unrelated (so its two gene
copies are never identical by descent through the previous generation). Let $F_t$ be the inbreeding
coefficient of an individual of generation $t$ relative to a base population at $t = 0$. Then

$$F_{t+1} = \frac{S}{2} (1 + F_t) \qquad (t \ge 0).$$

Consequently:

- for complete selfing ($S = 1$), $1 - F_t = 2^{-t} (1 - F_0)$, so $F_t \to 1$;
- for $0 \le S < 1$, the recursion has the unique fixed point $F^* = S/(2 - S)$, and
  $F_t - F^* = (S/2)^t (F_0 - F^*)$, so $F_t \to F^*$ geometrically for every $F_0 \in [0, 1]$.

Derivation: condition on how the individual was produced. If it was selfed (probability $S$), its two
genes are copies of the same parental gene with probability $1/2$, and then identical by descent, or
copies of the parent's two distinct genes with probability $1/2$, and then identical by descent with
probability $F_t$. If it was outcrossed (probability $1 - S$), its genes are not identical by descent.
Hence $F_{t+1} = S\,(\tfrac12 + \tfrac12 F_t) + (1 - S) \cdot 0$. Subtracting the fixed-point equation
$F^* = \tfrac{S}{2}(1 + F^*)$ gives $F_{t+1} - F^* = \tfrac{S}{2}\,(F_t - F^*)$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.9 "Regular Systems of Inbreeding: Selfing", equations (V-21)–(V-24), pp. 231–232
  (the case $S = 1$ and the first-step argument; the partial-selfing recursion and its solution are
  derived from that argument and are not stated in the source).
