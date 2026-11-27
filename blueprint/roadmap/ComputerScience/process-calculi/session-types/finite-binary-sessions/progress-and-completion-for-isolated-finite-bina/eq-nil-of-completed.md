# Typed thread with completed obligations is nil

Let $n$ be a natural number, $\Gamma$ a session context and $p$ a process. If $\Gamma \vdash_n p$
and $\Gamma(c) = \mathrm{end}$ for every channel number $c$, then $p = \mathbf{0}$.
