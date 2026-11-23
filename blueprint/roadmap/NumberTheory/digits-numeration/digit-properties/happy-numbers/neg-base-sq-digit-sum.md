# Sum of squared digits in a negative base

Let $b \le -2$ be an integer. Every integer $a$
has an expansion $a = \sum_{i=0}^{n} a_i b^i$ with digits $0 \le a_i \le |b| - 1$, unique up to
leading zero digits, and $S_{2,b}(a) = \sum_{i=0}^{n} a_i^2$ is the sum of the squares of these
digits. The digits are produced from the least significant one by taking $a_0 = a \bmod b$ and
passing to $(a - a_0)/b$, until $0$ is reached.

The definition is made for every integer $b$, by running this digit extraction for at most
$2|a| + 2$ steps; for $b \le -2$ this suffices, since the quantity $2a$ (for $a \ge 0$) or
$2|a| + 1$ (for $a < 0$) strictly decreases at each step.

## Sources

- Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2.
