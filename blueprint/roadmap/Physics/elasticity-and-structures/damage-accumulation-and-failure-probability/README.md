# Damage accumulation and failure probability

Finitely many scenarios $\omega$ carry nonnegative weights. In each scenario every component $i$ of
a finite set has a linear damage path $d_0(i, \omega) + r(i, \omega)\, t$ in time $t \ge 0$ and a
threshold $D(i, \omega)$, and it fails when its damage reaches the threshold, equality included. For
nonnegative rates and an increasing system event $S$, the system has failed by $t$ exactly when the
configuration of the components still below threshold is not in $S$. A sensor with gain $g \ne 0$
reads $g\, d + b + \varepsilon$ on one component, and conditioning on the reading lying in a bin $A$
of positive weight gives the system failure event $F$ the probability $P(A \cap F) / P(A)$; no
independence is assumed. The Palmgren–Miner damage sum $\sum_i n_i / N_i$ over finitely many cycle
classes with positive lives is an empirical index: no failure is asserted at any value of it.

## Linear damage paths and the system failure event

- [Linear damage path in each scenario](linear-damage.md)
- [Lifetime (D − d0) / r of a positive-rate linear path started below D](damage-lifetime-linear-damage.md)
- [For a nonnegative rate, failure by time t is exactly D ≤ d0 + r t](damage-lifetime-linear-damage-le-iff.md)
- [System failure event of linear damage paths at time t](system-failure-event.md)
- [Rates ≥ 0: monotone system failed by t iff its below-threshold set ∉ S](mem-system-failure-event-iff.md)

## The sensor reading and its bin

- [Sensor reading of a damage value with nonzero gain](sensor-reading.md)
- [The calibrated reading is the damage plus the error over the gain](gauge-strain-sensor-reading.md)
- [Scenarios whose reading lies in a closed bin](bin-event.md)
- [Bin membership of the sensor reading of a linear damage path](mem-bin-event-sensor-reading-iff.md)

## Conditional failure probability given a bin

- [Conditional failure probability given a bin, for nonnegative weights](prob-cond-weights-system-failure-event.md)

## The Palmgren–Miner damage sum

- [Palmgren–Miner damage sum over finitely many cycle classes](miner-damage.md)
- [Class counts aggregated from cycle records](cycle-class-counts.md)
- [Aggregating cycle records by class preserves total count and damage](miner-damage-cycle-class-counts.md)
- [A common change of cycle unit leaves the Miner damage sum unchanged](miner-damage-unit-change.md)
- [Nonnegative counts: Miner sum ≥ 0, equal to 0 exactly at zero counts](miner-damage-nonneg-and-eq-zero-iff.md)
- [Monotonicity of the Miner sum for nonnegative counts](miner-damage-mono.md)
- [With a zero life, the bare cycle-ratio sum ignores that class's count](bare-sum-at-zero-life-misreports.md)
