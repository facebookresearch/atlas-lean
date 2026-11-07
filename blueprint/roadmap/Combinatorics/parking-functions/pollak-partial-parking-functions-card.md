# Number of partial parking functions

Let $s$ and $t$ be natural numbers with
$0 < s \le t$. A partial parking function with $s$ cars and $t$ spots is a map
$f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ such that for every spot
$k \in \{0, \dots, t - 1\}$ at most $t - k$ cars $i$ have $f(i) \ge k$. The number of partial
parking functions with $s$ cars and $t$ spots is $(t + 1 - s)(t + 1)^{s - 1}$.

The proof is Pollak's circle argument.

## Sources

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats, “Lucky Cars and Lucky Spots in Parking Functions”, Journal of Integer Sequences 29 (2026), Article 26.1.1, proposition at lines 330–332 of https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex (independently verified; full source SHA-256 d166e7759bfd986aebf8bd5632479d9f5e4f11b28f5250ed1e5290851a8d6139, normalized no-final-newline proposition-span SHA-256 58e90130ad683625acf4a657d5bbbf145f2700065e2991cfd7084425783cc1fe).
