# Linear congruential generator

For parameters $q \ge 1$, $a$ coprime to $q$, $b$, and $w \ge 1$, the one-step *linear congruential generator* maps a seed $s \in \{0, \dots, q-1\}$ to

$$G_{\mathrm{lcg}}(s) = \bigl(\lfloor s / w \rfloor,\ (a s + b) \bmod q\bigr) \in R \times \{0, \dots, q-1\}, \qquad R = \{0, \dots, \lfloor (q-1)/w\rfloor\}.$$

Iterating the state update $s \mapsto as + b \bmod q$ and emitting $\lfloor s_i / w\rfloor$ at each step gives the multi-output generator.

## Depends on

- [PRG advantage](../pseudorandom-generators/prg-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
