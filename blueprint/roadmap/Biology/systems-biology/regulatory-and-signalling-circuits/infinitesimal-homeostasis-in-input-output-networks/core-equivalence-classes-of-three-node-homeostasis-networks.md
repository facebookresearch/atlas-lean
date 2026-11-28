# Core equivalence classes of three-node homeostasis networks

**Setting.** Input-output networks, admissible systems, the homeostasis matrix $H$ and core subnetworks are as in [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md) and [Core reduction and homeostasis types of input-output networks](core-reduction-and-homeostasis-types-of-input-output-networks.md). Two core networks are **core equivalent** if, for admissible systems with corresponding linearized couplings, their homeostasis matrices have the same determinant up to sign and relabeling, so they support the same infinitesimal homeostasis types. In an *input = output* network the input parameter enters the equation of the output node itself.

**Theorem 2.6.** There are exactly 3 core equivalence classes of 3-node input-output core networks with input node $\ne$ output node. Representatives are (i) the feedforward excitation motif, (ii) the substrate inhibition motif and (iii) the negative feedback motif.

**Theorem 4.11, Theorem 4.12 and Corollary 4.13.** There are 10 isomorphism classes of 3-node input = output core networks. For them $\det H$ factors according to the path components (strongly connected components) of the subnetwork of regulatory nodes: it is a single $2\times2$ Jacobian minor $f_{\sigma,x_\sigma}f_{\rho,x_\rho}-f_{\sigma,x_\rho}f_{\rho,x_\sigma}$ when the two regulatory nodes form one component, and a product of two linearized self-couplings $f_{\sigma,x_\sigma}f_{\rho,x_\rho}$ when they form two. Two such networks are core equivalent if and only if their condensation appendage networks have the same number of path components. In an input = output network every homeostasis type is of appendage type (Corollary 4.6: structural homeostasis does not exist).

**Corollary 4.14.** Combining both cases, there are 5 core equivalence classes of 3-node core networks: feedforward excitation, substrate inhibition and negative feedback (input $\ne$ output), and, for input = output, (iv) the 3-node loop motif $\iota\to\rho\to\sigma\to\iota$, whose regulatory nodes form two path components $\{\rho\}$, $\{\sigma\}$ ($\det H=f_{\rho,x_\rho}f_{\sigma,x_\sigma}$), and (v) the antithetic feedback motif (arrows $\iota\to\rho$, $\rho\to\sigma$, $\sigma\to\rho$, $\sigma\to\iota$), whose regulatory nodes form one path component ($\det H=f_{\sigma,x_\sigma}f_{\rho,x_\rho}-f_{\sigma,x_\rho}f_{\rho,x_\sigma}$). Every other 3-node core network is obtained from these five by adding or removing backward arrows.

## Depends on

- [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md)
- [Core reduction and homeostasis types of input-output networks](core-reduction-and-homeostasis-types-of-input-output-networks.md)

## Expansion

For three nodes with input $\ne$ output, $H$ is $2\times2$ and its determinant is either a sum of two path products (feedforward excitation: cancellation between the direct and the indirect path), a single self-coupling of the middle node (substrate inhibition: the middle node becomes insensitive), or a single coupling product around the feedback loop (negative feedback). Backward arrows do not enter $H$, so all 3-node core networks reduce to these three determinant shapes. For input = output networks $H$ is the Jacobian of the regulatory subnetwork, which factors over its strongly connected components, so only the number of components matters.

## Sources

- F. Antoneli, M. Golubitsky, J. Jin, I. Stewart, "Homeostasis in input-output networks: structure, classification and applications", *Mathematical Biosciences* 384 (2025), 109435, Theorem 2.6, Corollary 4.6, Theorem 4.11, Theorem 4.12, Corollary 4.13, Corollary 4.14, Examples 4.3–4.4 and Figure 22, <https://doi.org/10.1016/j.mbs.2025.109435> (preprint arXiv:2405.03861).
