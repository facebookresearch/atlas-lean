# Process capability indices

Let a quality characteristic have true mean $\mu$ and standard deviation $\sigma > 0$, and let the specification limits satisfy
$\mathrm{LSL} \le \mathrm{USL}$, with midpoint $m = (\mathrm{LSL} + \mathrm{USL})/2$. The capability indices are

$$C_p = \frac{\mathrm{USL} - \mathrm{LSL}}{6\sigma}, \qquad
C_{pk} = \min\Bigl(\frac{\mathrm{USL} - \mu}{3\sigma}, \frac{\mu - \mathrm{LSL}}{3\sigma}\Bigr) = C_p - \frac{\lvert \mu - m\rvert}{3\sigma}.$$

So $C_{pk} \le C_p$, with equality exactly when $\mu = m$. Zero-width limits give $C_p = 0$ and $C_{pk} \le 0$; reversed limits,
with an empty pass event, are excluded. Under a change of units $y = a + b x$ with $b > 0$, the pass event
$\{\mathrm{LSL} \le X \le \mathrm{USL}\}$ equals $\{a + b\,\mathrm{LSL} \le Y \le a + b\,\mathrm{USL}\}$, and with mean $a + b\mu$ and
standard deviation $b\sigma$ both indices are unchanged; $b < 0$ reverses the limits. For limits $[7, 13]$ and $\sigma = 1$,
$\mu = 10$ gives $C_p = C_{pk} = 1$ and $\mu = 11$ gives $C_{pk} = 2/3$. These are population quantities: replacing $\mu$ and
$\sigma$ by sample estimates needs a separate inference result.

## Depends on

## Proof depends on

## Sources

- NIST/SEMATECH *e-Handbook of Statistical Methods*, Section 6.1.6, process capability indices $C_p$ and $C_{pk}$ and $C_{pk} = C_p(1 - k)$, <https://www.itl.nist.gov/div898/handbook/pmc/section1/pmc16.htm>.
