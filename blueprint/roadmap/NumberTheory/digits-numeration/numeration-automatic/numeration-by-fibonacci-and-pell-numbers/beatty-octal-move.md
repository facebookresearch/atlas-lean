# Moves of the Beatty octal game

Let $\alpha$ and $\beta$ be real numbers. In the Beatty
octal game for $\alpha$ and $\beta$, a move takes a heap of $n$ tokens to a heap of $m$ tokens
exactly when one of the following holds: $n \ge 1$, $n = \lfloor k\alpha \rfloor$ for some
integer $k \ge 1$, and $m = 0$ (the whole heap is removed); or $m = n - i$ for some natural
number $i$ with $1 \le i < n$ and $i = \lfloor k\beta \rfloor$ for some integer $k \ge 1$
(removing $i$ tokens leaves a nonempty heap).

When $\alpha$ and $\beta$ are complementary, so that every $i \ge 1$ lies in exactly one of the
Beatty sequences $\{\lfloor k\alpha \rfloor : k \ge 1\}$ and
$\{\lfloor k\beta \rfloor : k \ge 1\}$, this is the octal game with code
$0{\cdot}d_1 d_2 d_3 \ldots$, where $d_i = 1$ if $i$ lies in the first sequence and $d_i = 2$ if
$i$ lies in the second.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1 (octal codes) and the codes of the gold, silver and bronze games in Sections 2, 3, 4.
