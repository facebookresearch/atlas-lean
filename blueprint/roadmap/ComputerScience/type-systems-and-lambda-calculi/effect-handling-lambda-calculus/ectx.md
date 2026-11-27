# Evaluation contexts

The hole, a `do` frame `do x ← E in c₂`, and a handler frame
`with h handle E` whose handler `h` is a handler literal `.hdl cr cls`
(Hillerström-Lindley 2016, §3.4, Fig. 7; Pretnar 2015, Fig. 3). A handler given by any other
value, such as a variable, never forms a frame. The hole is never under a binder.
