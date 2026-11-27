# Moulin–Ching characterization of strategy-proof rules on single-peaked preferences

A rule on ordinal single-peaked preferences over $[a, b]$ with finitely many agents is strategy-proof and onto if and only if it is a generalized median voter scheme applied to the reported peaks, i.e. of the form $\max_{S \subseteq N} \min(\beta_S, \min_{i \in S} p_i)$, with the convention $\min_{i \in \emptyset} p_i = b$, for coalition parameters $\beta_S \in [a, b]$ that are monotone ($\beta_S \le \beta_T$ whenever $S \subseteq T$) and satisfy $\beta_\emptyset = a$ and $\beta_N = b$. Every such rule is group strategy-proof in the strong sense.

## Proof sketch

By the peaks-only theorem the rule is a function of peaks, which is a strategy-proof onto facility-location rule on the interval, hence a generalized median voter scheme by Moulin's theorem; the max-min and min-max forms are dual.

For group strategy-proofness write $f(p) = \max_S v_S(p)$ with $v_S(p) = \min(\beta_S, \min_{i \in S} p_i)$, let $a = f(p)$ at the true peaks $p$, and let a coalition $C$ report $p'$ (agents outside $C$ unchanged) and move the outcome to $a' \ne a$. If $a' > a$, some term $v_S(p') > a$; it is not one with $S \cap C = \emptyset$, which is unchanged and at most $a$, so $\beta_S > a$ and $p_i > a$ for $i \in S \setminus C$. If every member of $C$ had $p_i > a$, then $v_S(p) > a = f(p)$, which is impossible; so some member has $p_i \le a < a'$. If $a' < a$, let $v_{S^*}(p) = a$ attain the maximum; if every member had $p_i < a$, then $S^*$ contains no member, so $v_{S^*}(p') = a$ and $a' \ge a$, which is impossible; so some member has $p_i \ge a > a'$. In both cases $a$ lies between that member's peak and $a'$ (or equals the peak), so by single-peakedness the member strictly prefers $a$ to $a'$ and is strictly worse off.

## Depends on

- [Ordinal single-peaked preferences on an interval](ordinal-single-peaked-preferences-on-an-interval.md)
- [Generalized median voter scheme on an interval](../../mechanism-design/facility-location-without-money/generalized-median-voter-scheme-on-an-interval.md)

## Proof depends on

- [Option sets are closed intervals; Ching's peaks-only theorem](option-sets-are-closed-intervals-chings-peaks-only-theorem.md)
- [Moulin's characterization of strategyproof location rules on an interval](../../mechanism-design/facility-location-without-money/moulins-characterization-of-strategyproof-location-rules-on-an-interval.md)

## Sources

- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007.
- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
- Stephen Ching, "Strategy-proofness and "median voters"", International Journal of Game Theory, 1997.
