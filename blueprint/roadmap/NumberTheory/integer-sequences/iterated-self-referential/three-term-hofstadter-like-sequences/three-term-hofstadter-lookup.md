# Value of a partially computed sequence at an index

Given computed terms
$B(1), \dots, B(m)$, a choice of whether the sequence is padded, and an integer $j$, the value
at index $j$ is $B(j)$ when $1 \le j \le m$, is $0$ when $j \le 0$ and the sequence is padded,
and is undefined otherwise (for $j \le 0$ in the unpadded case, and for $j > m$).

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1 (initial-condition and sequence-death conventions).
