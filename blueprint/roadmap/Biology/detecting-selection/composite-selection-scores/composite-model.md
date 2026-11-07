# Composite selection score model

A composite-score model (Grossman et al. 2010): a prior probability `prior` that the site
is under selection, and for each of the `k` component statistics a positive score function
`sel` under selection and `neut` under neutrality (unnormalized densities: only positivity is
assumed). Conditionally on the hypothesis the components are independent, which is what
makes the joint scores the products below. The Bayes/posterior reading of `posterior`
requires the additional normalization hypothesis of `sum_joint_eq_one`.
