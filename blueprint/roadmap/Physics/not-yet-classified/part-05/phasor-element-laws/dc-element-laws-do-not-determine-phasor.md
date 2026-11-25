# At zero frequency the element laws do not determine the phasor

For a phasor $V \in \mathbb{C}$ and angular frequency $\omega \in \mathbb{R}$, the RMS waveform is $w_{V,\omega}(t) = \sqrt{2}\, \operatorname{Re}\!\big(V e^{i\omega t}\big)$. At $\omega = 0$, with voltage phasor $V = i$, current phasor $I = 0$ and $R = L = 1$:

1. $w_{i,0}(t) = 1 \cdot w_{0,0}(t)$ for all $t$ (the resistor law holds), yet $i \ne 1 \cdot 0$;
2. $w_{i,0}(t) = 1 \cdot \frac{d}{dt} w_{0,0}(t)$ for all $t$ (the inductor law holds), yet $i \ne i \cdot 0 \cdot 1 \cdot 0$ (the phasor equation $V = i\omega L I$ fails).
