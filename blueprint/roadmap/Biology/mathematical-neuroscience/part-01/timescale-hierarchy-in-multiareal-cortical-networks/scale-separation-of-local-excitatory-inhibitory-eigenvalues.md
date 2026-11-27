# Scale separation of local excitatory–inhibitory eigenvalues

**Setting.** A multiareal firing-rate model has, in each of $n$ areas $i$, an excitatory rate $\nu_{E,i}$ and an inhibitory rate $\nu_{I,i}$ obeying

$$\tau_E \dot\nu_{E,i} = -\nu_{E,i} + \beta_E[I_{\mathrm{syn},E,i} + I_{\mathrm{ext},E,i}]_+, \qquad \tau_I \dot\nu_{I,i} = -\nu_{I,i} + \beta_I[I_{\mathrm{syn},I,i} + I_{\mathrm{ext},I,i}]_+,$$

with $[x]_+ = \max(x,0)$. In the linear (suprathreshold) regime this is $\dot\nu = W\nu + I_{\mathrm{ext}}$ with

$$W = \begin{pmatrix} D_{EE} + F_{EE} & D_{EI} \\ D_{IE} + F_{IE} & D_{II}\end{pmatrix},$$

where $D_{pq}$ are diagonal $n\times n$ matrices of local (intra-areal) couplings and $F_{EE}, F_{IE}$ carry long-range excitatory projections. Each area integrates input with the common set of time constants $\tau_i = -1/\operatorname{Re}\lambda_i$ over the eigenvalues $\lambda_i$ of $W$.

**Proposition (disconnected areas).** Let $D = \begin{pmatrix} D_{EE} & D_{EI}\\ D_{IE} & D_{II}\end{pmatrix}$ with diagonal blocks satisfying

$$D_{II},\ D_{IE} \text{ of exact order one},\quad D_{EI} = O(\epsilon),\quad D_{EE} = O(\epsilon)$$

(that is, $D_{II}$ and $D_{IE}$ have diagonal entries bounded and bounded away from $0$ uniformly in $\epsilon$), with $D_{II}$ having strictly negative diagonal entries (as in the cortical model), for a small parameter $\epsilon$ (in the cortical model $\epsilon = (\beta_E/\tau_E)/(\beta_I/\tau_I)$, small because inhibitory cells have steeper gain and faster membranes). Then $D$ has $n$ eigenvalues of order $O(\epsilon)$ and $n$ eigenvalues of order $O(1)$. Explicitly, $D = P\Lambda P^{-1}$ with

$$P = \begin{pmatrix} I + AB & -A \\ -B & I\end{pmatrix},\qquad \Lambda = \begin{pmatrix}\Lambda_U & 0\\ 0 & \Lambda_L\end{pmatrix},$$

where $A = -D_{EI}D_{II}^{-1} + O(\epsilon^2)$, $B = D_{IE}D_{II}^{-1} + O(\epsilon)$, and

$$\Lambda_U = D_{EE} - D_{EI}D_{II}^{-1}D_{IE} + O(\epsilon^2) = O(\epsilon),\qquad \Lambda_L = D_{II} + D_{EI}D_{II}^{-1}D_{IE} + O(\epsilon^2) = O(1).$$

**Interpretation.** The $O(1)$ eigenvalues give a fast timescale pool (a few milliseconds) that barely depends on the area's hierarchy level, because $D_{II}$ does not. The $O(\epsilon)$ eigenvalues give slow timescales; since $D_{EE}$ and $D_{IE}$ scale with the hierarchy value $h_i$, a gradient of synaptic excitation across areas spreads the slow pool. Without long-range coupling each slow eigenvector is supported on a single area (its excitatory part is a multiple of $e_k$; its inhibitory part $-B_k e_k$ is of order one), so each area has its own slow timescale.

## Expansion

Because all four blocks are diagonal, the problem decouples into $n$ independent $2\times 2$ matrices. $A$ solves the diagonal quadratic $-(D_{EE} + AD_{IE})A + D_{EI} + AD_{II} = 0$; choosing the root

$$A = \tfrac12 D_{IE}^{-1}\Big[D_{II} - D_{EE} + \sqrt{(D_{II}-D_{EE})^2 + 4D_{IE}D_{EI}}\Big]$$

and expanding in $\epsilon$ gives the stated orders; this root is the $O(\epsilon)$ one because $D_{II} - D_{EE} < 0$ for small $\epsilon$ (for $D_{II} > 0$ it would be the $O(1)$ root and $\Lambda_U$, $\Lambda_L$ would swap orders). $\Lambda_U$ is a Schur complement: the slow mode is excitation with inhibition slaved to it.

## Sources

- S. Li, X.-J. Wang, *Hierarchical timescales in the neocortex: Mathematical mechanism and biological insights*, Proc. Natl. Acad. Sci. USA 119 (2022), e2110274119, Eqs. 1–5 and Proposition 1. <https://doi.org/10.1073/pnas.2110274119> (PMCID: PMC8832993)
