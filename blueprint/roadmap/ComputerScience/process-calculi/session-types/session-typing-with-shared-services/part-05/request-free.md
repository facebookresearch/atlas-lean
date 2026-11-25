# Process with no exposed output on a declared shared name

Let $\Gamma$ be a service environment. Request-freeness for $\Gamma$ is defined by recursion:
$\mathbf{0}$ and every input are request-free; an output $\overline{a}\langle b\rangle.p$ is
request-free when $a$ is not $\mathrm{c}_s$ for any $s$ declared in $\Gamma$; $p \mid q$ and $p + q$
are request-free when $p$ and $q$ are; $\nu\,p$ and $!p$ are request-free when $p$ is. Continuations
of prefixes are not inspected.
