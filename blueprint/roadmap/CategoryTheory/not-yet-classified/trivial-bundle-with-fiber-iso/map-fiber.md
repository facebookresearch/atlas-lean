# Map Fiber

Fiber-side transport along a fiber isomorphism.

Given `e : F ≅ G` and a presentation `h` of `p` with fixed fiber `G`, this
builds a presentation of the same `p` with the same total object and base,
but fixed fiber `F` and second projection `h.r ≫ e.inv`. Only the fixed
fiber is changed along the supplied iso; no bundle gluing, descent, chart,
or model claim is made.
