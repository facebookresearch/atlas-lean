# Attenuation as log ratio

In the monochromatic model, take a positive incident intensity $I_0 > 0$ and a real line integral $L$ of the attenuation coefficient, and let the transmitted intensity be $I = I_0 e^{-L}$. Then

$$\log(I_0 / I) = L.$$

This is the same inversion as [monochromatic attenuation inversion](attenuation-log-inversion.md), written with the reciprocal ratio: since $\log(I_0 / I) = -\log(I / I_0)$, the two statements are equivalent forms of each other under the same hypotheses. The monochromatic assumption matters: for a mixture of energies the log of the transmitted fraction is not the mean attenuation (see [the two-energy mixture counterexample](mixture-log-ne-mean.md)).
