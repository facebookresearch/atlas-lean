# Exact Boyer–Moore cost when the pattern repeats one letter and ends in another, which alone makes up the text

**Exact Boyer–Moore cost when the pattern repeats one letter and ends in another, which alone
makes up the text.** Let $a \ne b$ be letters of the alphabet $\{0, \dots, \sigma - 1\}$ and let
$m$ and $n$ be natural numbers with $2 \le m \le n$. Write $a^{m-1}b$ for the word of $m - 1$
copies of $a$ followed by one $b$, and $b^n$ for the word of $n$ copies of $b$. The cost of the
Boyer–Moore matcher with pattern $a^{m-1}b$ and text $b^n$ equals
$m + n + P + 4\lfloor n/m \rfloor$, where $P$ is the cost of the Boyer–Moore preprocessing of
the pattern $a^{m-1}b$.

On these inputs every alignment makes two character tests and is followed by a shift by $m$.
