# Ramanujan's closed form for $\int_0^x du/(1 + u^8)$ (Chapter 8, Entry 14(vii))

Put
$s_\pm = \sqrt{2 \pm \sqrt2}$ and, for real $x$,
$R_\pm(x) = \frac{1 + s_\pm x + x^2}{1 - s_\pm x + x^2}$. For every real $x$ with $|x| < 1$, the
function $u \mapsto 1/(1 + u^8)$ is integrable on the interval between $0$ and $x$, $R_+(x) > 0$,
$R_-(x) > 0$, $1 - x^2 \ne 0$, and

$$\int_0^x \frac{du}{1 + u^8} = \frac{s_+}{16} \left( \log R_+(x) +
2 \arctan \frac{s_+ x}{1 - x^2} \right) + \frac{s_-}{16} \left( \log R_-(x) +
2 \arctan \frac{s_- x}{1 - x^2} \right).$$

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(vii), pp. 189–190. Proves `Wanted` entry `ramanujan_part1_ch8_entry14_vii_integral8`.
