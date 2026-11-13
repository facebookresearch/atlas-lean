# Expected number of lucky cars in weakly increasing parking functions

Let $n \ge 1$. Number
cars and spots from $0$, and encode a weakly increasing parking function of length $n$ as a
nondecreasing map $a : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $a(i) \le i$ for every $i$.
The average, over all such maps $a$, of the number of indices $i$ with $a(i) = i$ equals
$\frac{3n}{n+2}$. Here car $i$ parks in spot $i$ and is lucky exactly when $a(i) = i$, so this
number counts both the lucky cars and the lucky spots.

## Sources

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats, "Lucky Cars and Lucky Spots in Parking Functions," Journal of Integer Sequences 29 (2026), Article 26.1.1, Corollary, lines 631–633 (supporting lemma lines 619–629), https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex The corollary attributes the Dyck-path expectation value to Deutsch.
