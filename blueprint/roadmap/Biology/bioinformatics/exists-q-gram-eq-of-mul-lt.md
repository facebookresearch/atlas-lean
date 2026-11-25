# Words within Hamming distance $k$ share an aligned $q$-gram

Let $w$, $q$ and $k$ be natural numbers with $q \le w$ and $kq < w - q + 1$. Two words of length $w$ that differ in at
most $k$ positions share at least one positionally aligned [$q$-gram](q-gram.md): there is an offset
$i \in \{0, \dots, w - q\}$ at which their $q$-grams are equal. This is the case of the
[$q$-gram filtering lemma](q-gram-filtering-lemma-for-approximate-matching.md) in which its lower bound is positive.
