# Actual output level of a DAC with level errors

For a real step $\Delta$, a level-error function $e \colon \mathbb{Z} \to \mathbb{R}$ and an integer
code $k$, the actual output level of the digital-to-analog converter is

$$L(k) = \Delta k + e(k),$$

the ideal code-to-voltage value $\Delta k$ plus the level error at code $k$. In the physical reading
$\Delta > 0$ and the error is bounded, $|e(k)| \le \eta$, on a code range $[k_{\min}, k_{\max}]$;
the definition takes any real $\Delta$ and any errors.
