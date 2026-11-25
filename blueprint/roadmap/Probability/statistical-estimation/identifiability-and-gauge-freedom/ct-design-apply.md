# Linearity of the integral over a finite basis

Let $\mu$ be a measure on a measurable space $\alpha$ (not necessarily a probability measure), $s$ a
finite index set, $\varphi_i \colon \alpha \to \mathbb{R}$ functions and $x_i$ real coefficients,
with $\varphi_i$ integrable for $\mu$ for every $i \in s$. Then

$$\int \sum_{i \in s} x_i\, \varphi_i \, d\mu = \sum_{i \in s} x_i \int \varphi_i \, d\mu.$$

In the CT reading, $\mu$ is the measure along a ray, the $\varphi_i$ form a finite basis of
attenuation maps, and the line measurement of the superposition $\sum_i x_i \varphi_i$ is the design
sum of the basis measurements. This is forward linearity only; nothing is claimed about inverting
the design.
