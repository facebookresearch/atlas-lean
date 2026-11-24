# Progress for dual single-channel session threads

Let $\Gamma$ be a session context, $a$ a channel number and $r = (p,q)$ a pair of processes. If
$\Gamma \vdash_0 p$, $\overline{\Gamma} \vdash_0 q$ and $\Gamma(c) = \mathrm{end}$ for every $c \ne
a$, then either $r = (\mathbf{0}, \mathbf{0})$ or there is a pair $t$ with $r \to t$, a
communication step of binary configurations.

Without the single-channel hypothesis the statement fails: two threads with dual contexts can each
wait on a different channel.
