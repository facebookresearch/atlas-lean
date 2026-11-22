# Next term of the three-term Hofstadter-like recurrence

Given computed terms
$B(1), \dots, B(m)$, padded with $0$ at nonpositive indices or not, the next term is
$B(m + 1) = B(m + 1 - B(m)) + B(m + 1 - B(m - 1)) + B(m + 1 - B(m - 2))$. It is undefined
when one of the values it uses, $B(m)$, $B(m - 1)$, $B(m - 2)$ or one of the three summands,
sits at an undefined index: a nonpositive index in the unpadded case, or an index above $m$.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1.
