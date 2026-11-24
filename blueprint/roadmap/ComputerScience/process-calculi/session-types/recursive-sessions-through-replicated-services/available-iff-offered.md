# Availability as offers of all declared signatures

Let $\Gamma$ be a service environment and $p$ a process. All services of $\Gamma$ are available in
$p$ if and only if for every $s$ and service signature $\sigma$ with $\Gamma(s) = \sigma$, $p$
offers $s$ with signature $\sigma$ ($\Gamma(s) = \sigma$ and $p$ offers $\mathrm{c}_s$ persistently
through a replicated unguarded input).
