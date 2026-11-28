# Poisson survival function of the first assembly time with constant monomers

**Model.** In the stochastic Becker–Döring (SBD) model, $M$ identical particles in a finite volume aggregate one monomer at a time: clusters of size $k$ grow at rate $p_k$ times the monomer count and shrink at rate $q_{k+1}$, starting from the all-monomer state $C_k(0)=M\delta_{k,1}$. The *first assembly time* (FAT) $T^{N,M}$ is the first time a cluster of the maximal (nucleus) size $N$ appears. Total mass $\sum_kkC_k=M$ is conserved, which makes the SBD model nonlinear. In the *constant-monomer* formulation (CMSBD) the free monomer pool is clamped at $C_1\equiv M$:

$$\emptyset\ \underset{q_2}{\overset{p_1M(M-1)}{\rightleftharpoons}}\ C_2,\qquad C_k\ \underset{q_{k+1}}{\overset{p_kM}{\rightleftharpoons}}\ C_{k+1}\quad(k\ge2),$$

with $C_N$ absorbing ($p_N=q_N=0$).

**Result.** The CMSBD model is linear, so the counts $C_2(t),\dots,C_N(t)$ are independent Poisson variables whose means $c_k(t)=\mathbb E[C_k(t)]$, with $c_k(0)=0$, solve

$$\dot c_k=j_{k-1}-j_k\ (2\le k\le N-1),\qquad \dot c_N=j_{N-1},\qquad j_1=p_1M(M-1)-q_2c_2,\qquad j_k=p_kMc_k-q_{k+1}c_{k+1}\ (2\le k\le N-1),$$

where $q_N=0$, so $j_{N-1}=p_{N-1}Mc_{N-1}$. Write the transient vector as $\mathbf c=(c_2,\dots,c_{N-1})^\top$, indexed by $i=1,\dots,N-2$ with $\mathbf c_i=c_{i+1}$. Then $\dot{\mathbf c}=\mathbf A\mathbf c+\mathbf B$ with $\mathbf B=(p_1M(M-1),0,\dots,0)^\top$ and the tridiagonal $(N-2)\times(N-2)$ matrix $\mathbf A$ with entries

$$a_{i,i}=-(q_{i+1}+p_{i+1}M),\qquad a_{i+1,i}=p_{i+1}M,\qquad a_{i,i+1}=q_{i+2}.$$

For example, the first row gives $\dot c_2=p_1M(M-1)-(q_2+p_2M)c_2+q_3c_3$. The absorbing count is kept separate: $\dot c_N=p_{N-1}Mc_{N-1}$, so $c_N(t)=p_{N-1}M\int_0^tc_{N-1}(u)\,du$. Because $C_N$ is absorbing, the FAT survival function is

$$\mathbb P\bigl(T^{N,M}>t\bigr)=\mathbb P\bigl(C_N(t)=0\bigr)=e^{-c_N(t)} .$$

With $\tilde Q_m=\prod_{j=2}^m p_{j-1}/q_j$ and $D=\mathrm{diag}\bigl(\sqrt{\tilde Q_mM^m}\bigr)_{m=2}^{N-1}$, the matrix $D^{-1}\mathbf AD$ is symmetric, since $(d_{i+1}/d_i)^2=p_{i+1}M/q_{i+2}=a_{i+1,i}/a_{i,i+1}$. Hence $c_N(t)$ is explicit in terms of the real eigenvalues of a symmetric tridiagonal matrix, and the FAT moments follow by integrating $e^{-c_N(t)}$. (The printed matrix in the source repeats an index shift in the superdiagonal; the entries above follow from its flux equations.)

**Size dependence.** For the full mass-conserving SBD model with large $M$, a rescaling analysis shows that the mean FAT can depend only weakly on the total number of particles $M$, while its higher moments (variance, distribution shape) change markedly with $M$.

## Expansion

Linear birth–death–immigration networks started empty have Poisson marginals at all times (Kingman), and an absorbing top state turns the first-passage question into a zero-count question. The constant-monomer model approximates the full SBD model before the monomer pool depletes, i.e. for large $M$ up to the FAT.

## Sources

- Romain Yvinec, Samuel Bernard, Erwan Hingant and Laurent Pujo-Menjouet, "First passage times in homogeneous nucleation: dependence on the total number of particles", arXiv:1510.04730 (2015), section "Results and Analysis", subsection "Constant Monomer formulation" (FAT survival function) and the large-volume asymptotic subsections, <https://doi.org/10.48550/arXiv.1510.04730>.
