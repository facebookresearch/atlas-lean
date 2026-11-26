# Conditional log-likelihood of independent 1:1 pairs

For `n₁₀` pairs with the case
exposed and the control unexposed and `n₀₁` pairs with the reverse, the binary-exposure conditional
log-likelihood `n₁₀ log (e^β / (1 + e^β)) + n₀₁ log (1 / (1 + e^β))`. Each pair contributes the log
of its conditional probability given one case in the pair, and the sum is the joint conditional
log-likelihood when the pairs are independent of one another. The denominators `1 + e^β` are
always positive, so no division by zero occurs.
