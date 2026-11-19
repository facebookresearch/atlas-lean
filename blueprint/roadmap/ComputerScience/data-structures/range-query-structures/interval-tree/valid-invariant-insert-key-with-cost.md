# Keyed insertion preserves interval validity

Let $T$ be an interval tree in which every
stored interval $[a, b]$ satisfies $a \le b$, and let $e$ be an entry whose interval $[a, b]$
satisfies $a \le b$. Then the tree returned by keyed insertion of $e$ into $T$ also has every
stored interval $[a, b]$ satisfying $a \le b$.
