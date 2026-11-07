# Divide and conquer agrees with Kadane's algorithm

Let $\alpha$ be an additive monoid with
a linear order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$. For every list
$xs$ over $\alpha$, the divide-and-conquer maximum subarray algorithm and Kadane's algorithm
return the same result on $xs$.
