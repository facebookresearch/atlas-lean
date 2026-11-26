# DAC level contract

For a step $\Delta$ and a level error $e : \mathbb{Z} \to \mathbb{R}$, let $D(k) = \Delta k + e(k)$ be the DAC level of the integer code $k$. Let $\Delta > 0$, let $k_{\min}, k_{\max}$ be integers and $\eta$ real with $|e(k)| \le \eta$ for every integer $k \in [k_{\min}, k_{\max}]$. Let $\operatorname{round}$ round to the nearest integer with halves rounded up, let the ADC code of $x$ be $q(x) = \max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$, and call $x$ clipped when $\operatorname{round}(x/\Delta) < k_{\min}$ or $\operatorname{round}(x/\Delta) > k_{\max}$. Then:

1. for every integer $k$ with $k_{\min} \le k$ and $k + 1 \le k_{\max}$, $|D(k+1) - D(k) - \Delta| \le 2\eta$;
2. if $2\eta < \Delta$, then $D$ is strictly increasing on the integers of $[k_{\min}, k_{\max}]$;
3. for every real $x$ that is not clipped, $|D(q(x)) - x| \le \Delta/2 + \eta$.
