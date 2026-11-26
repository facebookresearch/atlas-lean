# Mass-action computation of least-squares linear regression

Real numbers are represented in *dual-rail* form as differences of two nonnegative concentrations, $a = [A^+] - [A^-]$. The basic catalytic mass-action modules have the desired value as the globally attracting steady state of an output species while the inputs act only as catalysts:

- **sum**: $X_i \to X_i + C$ for each input and $C \to 0$, giving $\dot{[C]} = \sum_i [X_i] - [C]$ and $[C]^{ss} = \sum_i [X_i]$;
- **product-sum**: $X_i + Y_i \to X_i + Y_i + C$ and $C \to 0$, giving $[C]^{ss} = \sum_i [X_i][Y_i]$;
- **division** (positive inputs): $A \to A + C$ and $B + C \to B$, giving $\dot{[C]} = [A] - [B][C]$ and $[C]^{ss} = [A]/[B]$.

Signed products follow from $(a^+ - a^-)(b^+ - b^-) = (a^+b^+ + a^-b^-) - (a^+b^- + a^-b^+)$. Stages are executed sequentially by gating each module with a clock species $O_k$ (each reaction carries $O_k$ as an extra catalyst) derived from a Hopf oscillator, so that each stage runs to steady state before the next starts.

**Proposition (generalized division).** For dual-rail inputs $A = A^+ - A^-$ and $B = B^+ - B^- \ne 0$, the composite network that (i) forms $|A| = \max(0, A^+ - A^-) + \max(0, A^- - A^+)$ and $|B|$ with subtraction and sum modules, (ii) applies the positive division module to get $|A|/|B|$, (iii) determines the signs of $A$ and $B$ with a comparison network followed by an approximate-majority amplifier, and (iv) routes $|A|/|B|$ to $C^+$ or $C^-$ by sign products, produces outputs with $C^+ - C^- = A/B$.

**Least-squares regression.** For data $(x_i,y_i)_{i=1}^n$, chaining these modules computes $\Sigma_x, \Sigma_y, \Sigma_{xx}, \Sigma_{xy}$, then $P_1 = n\Sigma_{xy}, P_2 = \Sigma_x\Sigma_y, P_3 = n\Sigma_{xx}, P_4 = \Sigma_x^2$, and finally, by subtraction and generalized division, the ordinary least-squares slope and intercept

$$\hat w = \frac{n\Sigma_{xy} - \Sigma_x \Sigma_y}{n\Sigma_{xx} - \Sigma_x^2}, \qquad \hat b = \frac{\Sigma_y - \hat w\, \Sigma_x}{n},$$

as differences of steady-state concentrations (provided the $x_i$ are not all equal). The same modules implement linear interpolation between data points and, with a gradient-descent loop, multivariate regression.

## Depends on

- [CRNs as computing devices](../crns-as-computing-devices.md)

## Expansion

Every module is a linear ODE in its output species with the inputs frozen as catalysts, so the output converges exponentially to the stated value during its clock phase; this is the steady-state (rate-independent on the output) computation paradigm for deterministic mass-action networks. Division is the only operation that cannot be written as nonnegative sums of products of dual-rail components, which is why the sign is separated from the magnitude: the comparison and approximate-majority subnetwork drives Boolean indicator species to $0$ or $1$, and the final products with these indicators assign the magnitude to the correct rail. Correctness is idealized: it assumes each stage reaches steady state within its clock phase and that the majority amplifier resolves the sign, which fails when $A^+ \approx A^-$.

## Sources

- Aryan Kumar, Amey Choudhary, Jiaxin Jin, Chittaranjan Hens, "Implementation of Linear Regression and Linear Interpolation using Reaction Networks", arXiv:2606.12573 (2026), Section 3 (modules), Section 4 and Proposition 5 (correctness of the generalized division algorithm), Sections 5 and 6, <https://doi.org/10.48550/arXiv.2606.12573>
