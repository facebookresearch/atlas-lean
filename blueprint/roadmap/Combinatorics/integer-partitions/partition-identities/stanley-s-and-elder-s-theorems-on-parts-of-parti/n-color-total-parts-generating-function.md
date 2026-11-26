# Generating functions for the total number of parts of $n$-color partitions

For
$m \ge 0$ let $T_o(m)$ (resp. $T_e(m)$) be the total number of parts, counted with
multiplicity, over the $n$-color partitions of $m$ having an odd (resp. even) number of parts.
Then, as formal power series in $q$ with rational coefficients,

$$\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{m \ge 0} \bigl(T_o(m) + T_e(m)\bigr) q^m$$

and

$$\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\prod_{m \ge 1} (1 + q^m)^m \sum_{m \ge 0} \bigl(T_o(m) - T_e(m)\bigr) q^m.$$

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 3.
