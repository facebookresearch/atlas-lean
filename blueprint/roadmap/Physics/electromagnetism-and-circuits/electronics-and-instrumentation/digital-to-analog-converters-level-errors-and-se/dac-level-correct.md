# Step, monotonicity and ADC-to-DAC error bounds for a DAC

Let $\Delta > 0$ and $\eta$ be real numbers, $k_{\min}$ and $k_{\max}$ integers, and
$e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [k_{\min}, k_{\max}]$. Then the [actual DAC levels](dac-level.md) $L(k) = \Delta k + e(k)$
satisfy all of the following.

- For every integer $k$ with $k_{\min} \le k$ and $k + 1 \le k_{\max}$,
  $|L(k + 1) - L(k) - \Delta| \le 2\eta$.
- If $2\eta < \Delta$, then $L$ is strictly increasing on the integer codes of
  $[k_{\min}, k_{\max}]$.
- For every input $x$ that the saturating converter does not clip, that is, with
  $k_{\min} \le \operatorname{round}(x/\Delta) \le k_{\max}$ where
  $\operatorname{round}(y) = \lfloor y + 1/2 \rfloor$,
  $|L(\operatorname{code}(x)) - x| \le \Delta/2 + \eta$, with
  $\operatorname{code}(x) = \max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$.
