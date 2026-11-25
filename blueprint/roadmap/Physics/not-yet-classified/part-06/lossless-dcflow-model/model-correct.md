# Lossless DC load-flow model

For branch susceptances $b_e > 0$ and node angles $\theta$: the DC flow is $f_e = b_e(\theta_{\text{tail}(e)} - \theta_{\text{head}(e)})$; the DC injection is $L_b \theta$ with $L_b = B\,\mathrm{diag}(b)\,B^\top$ the full weighted Laplacian; the lossless unit-magnitude AC sending-end real power is $P_e = b_e \sin(\theta_{\text{tail}(e)} - \theta_{\text{head}(e)})$; and $|P_e - f_e| \le b_e |\theta_{\text{tail}(e)} - \theta_{\text{head}(e)}|^3/6$ on every branch.
