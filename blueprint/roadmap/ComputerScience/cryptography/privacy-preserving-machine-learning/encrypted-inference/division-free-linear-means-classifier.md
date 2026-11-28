# Division-free integer linear means classifier

The *division-free integer* (DFI) linear means score replaces the class means of the linear means classifier by class sums cross-multiplied by the class sizes. On integer-encoded data it is a degree-2 integer polynomial with the same sign as the exact score, so a key holder who receives it encrypted and takes the sign gets the exact classifier's prediction.

A learning or prediction algorithm $A:(\mathbb{R}^n\times Y)^m\times\mathbb{R}^n\to Y$ is *$D$-polynomial* if it is a polynomial of degree at most $D$ in its arguments; a classifier is handled as $A=g\circ f$ with a real score $f$ evaluated under encryption and a discretization $g$ applied by the key holder. Let integer-encoded training examples $(x_i,y_i)$ have $x_i\in\mathbb{Z}^n$, $y_i\in\{+1,-1\}$, and let $I_y=\{i:y_i=y\}$, $m_y=|I_y|\ge1$ and $s_y=\sum_{i\in I_y}x_i$. The *linear means* score uses $\mu_y=s_y/m_y$, $w^*=\mu_{+1}-\mu_{-1}$, $x_0=(\mu_{+1}+\mu_{-1})/2$, $c^*=w^{*T}x_0$ and $f^*(x)=w^{*T}x-c^*$. The DFI score is

$$
\tilde w=m_{-1}s_{+1}-m_{+1}s_{-1}=m_{+1}m_{-1}w^*,\qquad \tilde x_0=m_{-1}s_{+1}+m_{+1}s_{-1}=2m_{+1}m_{-1}x_0,
$$

$$
\tilde c=\tilde w^{T}\tilde x_0=2m_{+1}^2m_{-1}^2c^*,\qquad \tilde f(x)=2m_{+1}m_{-1}\tilde w^{T}x-\tilde c=2m_{+1}^2m_{-1}^2f^*(x).
$$

With the grouping of the examples and the class sizes known to the evaluator (not necessarily which group carries which label), $\tilde f$ has integer coefficients and total degree $2$ in the entries of the training vectors and of $x$, and $\mathrm{sign}\,\tilde f(x)=\mathrm{sign}\,f^*(x)$ for every $x$, zero included. These equalities are for the integer-encoded data; relative to the original real data the encoding is an approximation.

## Depends on

None.

## Proof depends on

None.

## Expansion

Substitute $s_y=m_y\mu_y$; each identity is a one-line expansion. Correct homomorphic evaluation additionally needs the integer range and noise conditions of the chosen scheme.

## Sources

- Thore Graepel, Kristin Lauter, Michael Naehrig, "ML Confidential: Machine Learning on Encrypted Data", ICISC 2012, LNCS 7839 (2013), DOI 10.1007/978-3-642-37682-5_1; numbers from IACR ePrint 2012/323: Definition 1, §3.1 and §3.2 (Equation 3).
