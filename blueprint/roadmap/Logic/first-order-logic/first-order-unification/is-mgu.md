# Most general unifier

A substitution $s$ is a most general unifier of a list of
equations $E$ when $s$ unifies $E$ and every unifier $s'$ of $E$ factors through $s$, that is,
$s' = s \gg r$ for some substitution $r$, where $s \gg r$ applies first $s$ and then $r$.
