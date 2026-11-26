# Normal–exponential background correction

Microarray foreground intensities contain ambient fluorescence that background subtraction removes only partly. The normexp model writes the background-subtracted intensity as normally distributed residual background plus exponentially distributed true signal; the corrected intensity is the conditional mean of the signal given the observation, which is always positive, and the three parameters are estimated per channel by maximum likelihood, with a saddle-point approximation providing reliable starting values.

- [Normal–exponential convolution density and signal posterior mean](normexp-convolution-density-and-signal-posterior-mean.md)
- [Saddle-point approximation of the normal–exponential density](saddle-point-approximation-of-the-normexp-density.md)
