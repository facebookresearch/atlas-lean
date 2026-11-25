# Structural congruence of π-calculus processes

Structural congruence $\equiv$ is the smallest equivalence relation on [processes](proc.md) that is closed under parallel composition, restriction, choice, output and input prefixes and replication (if $P \equiv P'$ and $Q \equiv Q'$ then $P \mid Q \equiv P' \mid Q'$, $\nu P \equiv \nu P'$, $P + Q \equiv P' + Q'$, $\bar{a}\langle b\rangle.P \equiv \bar{a}\langle b\rangle.P'$, $a(\cdot).P \equiv a(\cdot).P'$ and $!P \equiv\ !P'$) and contains:

- $P \mid Q \equiv Q \mid P$, $(P \mid Q) \mid R \equiv P \mid (Q \mid R)$ and $P \mid \mathbf{0} \equiv P$;
- scope extrusion $(\nu P) \mid Q \equiv \nu\,(P \mid \uparrow_0 Q)$, where the [lifting](lift-proc.md) $\uparrow_0 Q$ ensures that $Q$ does not mention the fresh name;
- $\nu \mathbf{0} \equiv \mathbf{0}$;
- $\nu \nu P \equiv \nu \nu\, (P[0 \leftrightarrow 1])$: nested restrictions commute, [swapping](swap-proc.md) the two bound indices;
- $!P \equiv P \mid\ !P$: replication unfolds.
