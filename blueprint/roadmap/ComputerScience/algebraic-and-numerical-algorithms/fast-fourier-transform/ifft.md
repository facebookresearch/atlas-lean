# Inverse FFT by conjugation

Let $R$ be a field that is a star ring, with star operation
$z \mapsto \bar z$. For a natural number $d$, an element $\omega \in R$ and a vector
$x \in R^{2^d}$, the inverse FFT conjugates every entry of $x$, applies the radix-two FFT with
root $\omega$, conjugates every entry of the result, and multiplies every entry by the inverse
$(2^d)^{-1}$ of $2^d$ in $R$ (which is $0$ when $2^d = 0$ in $R$). It charges $3 \cdot 2^d$
operations for each of the two conjugation passes and for the scaling pass, one operation for
computing $(2^d)^{-1}$, and the cost of the FFT.
