# Completed sole protocol means both threads are nil

Let $\Gamma$ be a session context, $a$ a channel number and $r = (p,q)$ a pair of processes. If
$\Gamma \vdash_0 p$, $\overline{\Gamma} \vdash_0 q$, $\Gamma(c) = \mathrm{end}$ for every $c \ne a$
and $\Gamma(a) = \mathrm{end}$, then $r = (\mathbf{0}, \mathbf{0})$.
