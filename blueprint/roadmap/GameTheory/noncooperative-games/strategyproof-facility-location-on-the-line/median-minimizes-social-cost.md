# Median minimizes social Cost

For `n ≥ 1` agents with locations `x : Fin n → ℝ`, placing the facility at the median of the reports (the element of rank `⌊(n - 1)/2⌋`, counting from `0`, in sorted order) minimizes the social cost: `∑ᵢ |median x - x i| ≤ ∑ᵢ |y - x i|` for every `y`.
