# Receiving a closed name preserves session typing

Let $\Gamma$ be a session context, $p$ a process and $b$ a name that is a free channel constant
(scoped at depth $0$). If $\Gamma \vdash_1 p$, then $\Gamma \vdash_0 p\{b\}$, where $p\{b\}$
replaces the variable $0$ of $p$ by $b$ and lowers every larger variable index by one.
