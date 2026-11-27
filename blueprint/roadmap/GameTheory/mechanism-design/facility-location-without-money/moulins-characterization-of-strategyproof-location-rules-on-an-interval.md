# Moulin's characterization of strategyproof location rules on an interval

On a compact interval $[a, b]$ with $a < b$ (or any metric space isometric to one) and finitely many agents with distance costs, a deterministic facility-location mechanism is strategyproof and onto if and only if it is a generalized median voter scheme. It is moreover anonymous if and only if it is a phantom median rule with $n - 1$ phantoms.

## Proof sketch

Strategyproof onto rules are peaks-only and their option sets are intervals; recording, for each coalition, the outcome when exactly that coalition reports $b$ and the rest report $a$ yields the phantom parameters, and strategyproofness forces the min-max formula. Anonymity makes $\alpha_S$ depend only on $|S|$.

Every generalized median voter scheme is moreover group strategyproof in the strong sense: any joint misreport by a coalition that changes the outcome makes some member strictly worse off. Write the scheme as $f(x) = \min_S w_S(x)$ with $w_S(x) = \max(\alpha_S, \max_{i \in S} x_i)$, let $a = f(x)$ at the true peaks $x$, and let the coalition $C$ move the outcome to $a'$. If $a' < a$ and every member had $x_i < a$, then each term $w_S$ with $S \cap C \ne \emptyset$ already satisfied $\max(\alpha_S, \max_{i \in S \setminus C} x_i) \ge a$, so no misreport of the members brings any term below $a$, and $a' \ge a$; hence some member has $x_i \ge a > a'$ and is strictly worse off. If $a' > a$ and every member had $x_i > a$, then the term $w_{S^*}(x) = a$ attaining the minimum contains no member, so it is unchanged and $a' \le a$; hence some member has $x_i \le a < a'$ and is strictly worse off.

## Depends on

- [Generalized median voter scheme on an interval](generalized-median-voter-scheme-on-an-interval.md)

## Proof depends on

- [Order-statistic mechanisms on the line](order-statistic-mechanisms-on-the-line.md)

## Sources

- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007, Theorem 10.2 (strategyproof, onto and anonymous rules are the medians with $n - 1$ phantoms), Definition 10.3 and Theorem 10.4 (strategyproof and onto rules are the generalized median voter schemes).
