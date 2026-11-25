# Phasor form of the resistor, inductor and capacitor laws

For a phasor $V \in \mathbb{C}$ and angular frequency $\omega \in \mathbb{R}$, the RMS waveform is $w_{V,\omega}(t) = \sqrt{2}\, \operatorname{Re}\!\big(V e^{i\omega t}\big)$. Let $R \ge 0$, $L > 0$, $C > 0$ and $\omega > 0$, let $V, I \in \mathbb{C}$, and let $v, i : \mathbb{R} \to \mathbb{R}$ satisfy $v(t) = w_{V,\omega}(t)$ and $i(t) = w_{I,\omega}(t)$ for all $t$. Then

- $v(t) = R\, i(t)$ for all $t$ if and only if $V = R I$;
- $v(t) = L\, i'(t)$ for all $t$ if and only if $V = i\omega L\, I$;
- $i(t) = C\, v'(t)$ for all $t$ if and only if $I = i\omega C\, V$.
