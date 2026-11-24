# Rescaled spatial heat derivative

Let $P_t f$ be the whole-line Gaussian heat evolution and
$K_1(y)=(4\pi)^{-1/2}e^{-y^2/4}$ its time-one kernel.

If $f$ is Lebesgue almost-everywhere strongly measurable and has at most exponential
spatial growth, then for every $t>0$ and $x\in\mathbb R$,

$$
\partial_x P_t f(x)=-\frac1{2\sqrt t}\int_{\mathbb R} yK_1(y)f(x-\sqrt t\,y)\,dy.
$$

Here exponential growth means $|f(y)|\le M e^{c|y|}$ for some $M,c\ge0$.
The derivative is the actual derivative of the existing heat evolution; the datum
may be discontinuous. The proof rewrites the Gaussian-moment derivative as a
centered-kernel integral, translates, and rescales. Positive time is essential.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
