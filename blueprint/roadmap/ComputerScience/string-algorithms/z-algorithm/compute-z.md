# Z-algorithm

Given a word $s = s_0 \dots s_{n-1}$ over a type $\alpha$ with a Boolean
equality test, Gusfield's Z-box algorithm returns an array $Z$ of $n$ natural numbers with
$Z_0 = n$. It visits $i = 1, \dots, n - 1$ in turn, keeping a box $[\ell, r)$, initially empty,
that is the rightmost match of a prefix of $s$ found so far. If $\ell \le i < r$ and
$Z_{i - \ell} < r - i$, it sets $Z_i = Z_{i - \ell}$. Otherwise it finds $Z_i$ by comparing
symbols directly, starting at offset $r - i$ if $i < r$ and at offset $0$ if not, and if
$Z_i > 0$ the box becomes $[i, i + Z_i)$. When the equality test is lawful, $Z_i$ is the length
of the longest common prefix of $s$ and its suffix $s_i \dots s_{n-1}$. The cost counts one unit
for each visited position $i \ge 1$ and one unit for each symbol comparison; on the empty word the
result is empty with cost $0$.
