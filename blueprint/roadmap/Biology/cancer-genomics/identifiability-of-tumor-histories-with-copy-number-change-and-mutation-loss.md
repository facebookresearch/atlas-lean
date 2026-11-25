# Identifiability of tumor histories with copy-number change and mutation loss

This node records a research direction: when do different clonal histories of a tumor produce the same sequencing observations, once the infinite-sites assumption fails because of copy-number changes and loss of mutations?

## What would settle it

Fix an event model (copy-number gains and losses, mutation loss), the purity and sampling assumptions, and the map from a clonal history to observed data. Then characterize the histories with the same observations up to relabeling of clones, prove injectivity for a stated restricted class of histories, or construct explicit indistinguishable histories outside it.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Pradhan and El-Kebir show that the perfect phylogeny mixture problem, which reconstructs a tumor tree from mutation frequencies of bulk samples under the perfect phylogeny model, typically has multiple solutions, and give a polynomial-time computable upper bound on the number of solutions. El-Kebir et al. model copy-number evolution by segmental deletions and amplifications, give a pseudo-polynomial algorithm for a parental profile minimizing the total event distance to two children, and prove the tree version NP-hard. Neither paper treats identifiability for the combined event model.

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- S. Pradhan and M. El-Kebir, "On the non-uniqueness of solutions to the perfect phylogeny mixture problem", RECOMB Comparative Genomics 2018, abstract. <https://www.el-kebir.net/public/preprints/RECOMBCG18_Pradhan_El-Kebir.pdf>
- M. El-Kebir et al., "Complexity and algorithms for copy-number evolution problems", Algorithms for Molecular Biology 12 (2017), article 13, abstract. <https://pmc.ncbi.nlm.nih.gov/articles/PMC5433102/>
