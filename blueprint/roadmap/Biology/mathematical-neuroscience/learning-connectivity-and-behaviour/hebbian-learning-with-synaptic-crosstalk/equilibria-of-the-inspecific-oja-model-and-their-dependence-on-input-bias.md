# Equilibria of the inspecific Oja model and their dependence on input bias

**Model.** A linear neuron with weight vector $\mathbf w \in \mathbb R^n$ receives zero-mean inputs with covariance matrix $\mathbf C$ and learns by Oja's normalized Hebbian rule. Synaptic crosstalk spreads each Hebbian update: a fraction $q$ stays at the intended synapse and $\epsilon$ leaks to each other synapse, through the error matrix

$$\mathbf E = \begin{pmatrix} q & \epsilon & \cdots & \epsilon\\ \epsilon & q & \cdots & \epsilon\\ \vdots & & \ddots & \vdots\\ \epsilon & \epsilon & \cdots & q\end{pmatrix}, \qquad q + (n-1)\epsilon = 1, \quad 0 < \epsilon < \tfrac1n < q < 1.$$

The inspecific Oja equations are

$$\frac{d\mathbf w}{dt} = \gamma\big[\mathbf E\mathbf C\mathbf w - (\mathbf w^\top\mathbf C\mathbf w)\,\mathbf w\big].$$

Inputs are taken with covariance

$$\mathbf C = \begin{pmatrix} v+\delta_1 & \pm c & \cdots & \pm c\\ \pm c & v+\delta_2 & \cdots & \pm c\\ \vdots & & \ddots & \vdots\\ \pm c & \pm c & \cdots & v+\delta_n\end{pmatrix}, \qquad \delta_1 \ge \delta_2 \ge \dots \ge \delta_n \ge 0,$$

where the $\delta_j$ are input biases (some inputs more variable than others) and $\pm c$ the background correlations; for $2 \le k \le n$ the input has *bias loss of order $k$* if $\delta_1 = \dots = \delta_k$.

**Equilibria.** $\mathbf w$ is an equilibrium iff $\mathbf E\mathbf C\mathbf w = (\mathbf w^\top\mathbf C\mathbf w)\mathbf w$, i.e. $\mathbf w$ is an eigenvector of $\mathbf E\mathbf C$ normalized in the $\mathbf C$-norm $\|\mathbf w\|_{\mathbf C} = \sqrt{\mathbf w^\top\mathbf C\mathbf w}$, with eigenvalue $\lambda_{\mathbf w} = \|\mathbf w\|_{\mathbf C}^2$. Without crosstalk ($q = 1$) these are the principal components of the input, and learning extracts the leading one.

**Propositions.**
1. When all off-diagonal covariances equal a common value $c$ and the biases are distinct, $\delta_1 > \delta_2 > \dots > \delta_n$, $\mathbf E\mathbf C$ has $n$ real, distinct eigenvalues $\xi_1 > \xi_2 > \dots > \xi_n$, so the learning outcome remains a well-defined (crosstalk-distorted) principal direction. Mixed signs can break this: for $n = 3$, $v = 1$, $\mathbf C_{12} = c$, $\mathbf C_{13} = \mathbf C_{23} = -c$ with $c \approx 0.112185$, $\delta \approx (1.7032, 1.0574, 0.9871)$ and $\epsilon \approx 0.0534396$, $\mathbf E\mathbf C$ has a double eigenvalue near $1.76273$.
2. When all off-diagonal covariances equal a common value $c < 0$ and the biases are distinct, the critical error levels

$$\epsilon_j^* = \frac{-c}{v + \delta_j - c}, \qquad 0 < \epsilon_1^* < \epsilon_2^* < \dots < \epsilon_n^*,$$

are where the auxiliary functions $f_j(\epsilon)$ locating the eigenvalues of $\mathbf E\mathbf C$ change sign ($f_j > 0$ iff $\epsilon > \epsilon_j^*$). If moreover $v + \delta_n > (n-1)|c|$, so that $\epsilon_n^* < 1/n$, then as $\epsilon$ increases from $0$ to $1/n$ it crosses all of them in order (without this condition it crosses, in order, those $\epsilon_j^*$ that lie below $1/n$), and between consecutive critical values the eigenvalues interlace differently with the diagonal values $(q-\epsilon)(v + \delta_j - c)$.
3. For $\epsilon < \epsilon_1^*$ and $2 \le k \le n$, a bias loss of order $k$ ($\delta_1 = \dots = \delta_k$) produces a leading eigenvalue of multiplicity $k-1$ for $\mathbf E\mathbf C$. For $k = 2$ this eigenvalue is simple, so the learned direction stays unique; for $3 \le k \le n$ its multiplicity is at least $2$, so the learned direction is no longer unique.

## Proof sketch

Projecting the Oja flow onto the eigenbasis of $\mathbf E\mathbf C$ shows that the component along the largest eigenvalue grows relative to the others while the cubic term keeps $\|\mathbf w\|_{\mathbf C}$ bounded, as in the specific case; crosstalk enters only by replacing $\mathbf C$ with the non-symmetric $\mathbf E\mathbf C$. Since $\mathbf E = (q - \epsilon)\mathbf I + \epsilon\mathbf J$ with $\mathbf J$ the all-ones matrix, the characteristic polynomial of $\mathbf E\mathbf C$ factors through the diagonal entries $(q-\epsilon)(v + \delta_j - c)$ plus a rank-one correction, and the sign changes of the functions $f_j(\epsilon)$ vanishing at $\epsilon_j^*$ locate its roots between consecutive diagonal values. Equal biases make some of these diagonal values coincide, which produces the repeated leading eigenvalue. Biologically, input statistics with strong correlations or equal biases make crosstalk more disruptive to feature extraction in cortical learning.

## Sources

- Anca Rădulescu, "Input Statistics and Hebbian Cross-Talk Effects", *Neural Computation* 26 (2014), 654–692, <https://doi.org/10.1162/neco_a_00565>. Preprint version: arXiv:1208.2100 (2012), inspecific Oja model and error matrix, covariance family, and the propositions on eigenvalues of $\mathbf E\mathbf C$ under bias and bias loss, <https://doi.org/10.48550/arXiv.1208.2100>.
