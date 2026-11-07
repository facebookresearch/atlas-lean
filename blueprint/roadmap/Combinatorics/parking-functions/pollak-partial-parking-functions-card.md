# Number of partial parking functions

Let $s$ and $t$ be natural numbers with
$0 < s \le t$. A partial parking function with $s$ cars and $t$ spots is a map
$f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ such that for every spot
$k \in \{0, \dots, t - 1\}$ at most $t - k$ cars $i$ have $f(i) \ge k$. The number of partial
parking functions with $s$ cars and $t$ spots is $(t + 1 - s)(t + 1)^{s - 1}$.

The proof is Pollak's circle argument.

## Sources

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats, “Lucky Cars and Lucky Spots in Parking Functions”, Journal of Integer Sequences 29 (2026), Article 26.1.1, proposition at lines 330–332 of https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex.
