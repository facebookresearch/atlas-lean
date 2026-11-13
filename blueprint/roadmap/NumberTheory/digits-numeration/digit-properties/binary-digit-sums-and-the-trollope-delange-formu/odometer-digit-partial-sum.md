# Odometer partial sums

Let $q \in \mathbb{C}$, let $\omega = (\omega_0, \omega_1, \dots)$ be
a dyadic integer written as its binary digit sequence, let $T$ be the dyadic odometer
$T\omega = \omega + 1$, and let $s_q(\omega) = \sum_{i \ge 0} \omega_i q^{i+1}$, taken to be $0$
when the series is not absolutely summable. For real $x$ the odometer partial sum is

$$S_{q,\omega}(x) = \sum_{j < \lfloor x \rfloor_+} s_q(T^j \omega) +
\{x\} \, s_q(T^{\lfloor x \rfloor_+} \omega),$$

where $\lfloor x \rfloor_+ = \max(\lfloor x \rfloor, 0)$ and $\{x\} = x - \lfloor x \rfloor$. So
$S_{q,\omega}(n) = \sum_{j < n} s_q(T^j \omega)$ for every natural number $n$, and for $x \ge 0$
the function $S_{q,\omega}$ interpolates these values linearly between consecutive integers.

## Sources

- Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Sections 4 and 5.
