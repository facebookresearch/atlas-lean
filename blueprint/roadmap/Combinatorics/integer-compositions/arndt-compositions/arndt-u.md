# The map $U$ on lists

The map $U$ sends a list $(c_1, c_2, \dots)$ of natural
numbers to the concatenation of the images of its consecutive pairs $(c_1, c_2)$, $(c_3, c_4)$,
and so on, where $1^j$ denotes $j$ parts equal to $1$: a pair $(a, b)$ with $b < a$ goes to
$(1^{a - b - 1}, 2b + 1)$; a pair $(a, b)$ with $b \ge a$ goes to $(1^{a + b - 2k}, 2k)$, where
$k = \lfloor (b - a)/2 \rfloor + 1$ is the integer $k \ge 1$ with $2k - 2 \le b - a < 2k$; and a
final unpaired entry $a$ goes to $1^a$. The empty list goes to itself. The exponent
$a + b - 2k$ is read as $0$ when it is negative, which happens only when $a = 0$.

## Sources

- Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26 (2026), Article A64, Theorem 2 and its proof.
