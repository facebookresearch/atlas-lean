# `L²` error estimate

`‖u - u_h‖²_{L²(0,1)} ≤ (h / π)⁴ ‖f‖²_{L²(0,1)}`,
so the `L²` error is `O(h²)`. The proof uses nodal exactness and Wirtinger's
inequality on each element, not the Aubin–Nitsche duality argument.
