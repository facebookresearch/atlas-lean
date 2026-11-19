# Composition of simply typed substitutions

For substitutions $\sigma$ from a context
$\Gamma$ to $\Delta$ and $\tau$ from $\Delta$ to $\Xi$, the composite of $\sigma$ followed by
$\tau$ is the substitution from $\Gamma$ to $\Xi$ that sends each variable $x$ of $\Gamma$ to the
term obtained by applying $\tau$ to $\sigma(x)$.
